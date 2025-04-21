import streamlit as st
import requests
from bs4 import BeautifulSoup
from urllib.parse import urljoin, urlparse, parse_qs, unquote, quote, urlunparse
from collections import deque
import csv
import datetime
import re
import time
from io import StringIO
import json
import hashlib
import html
import logging
import tldextract
from urllib3.util import Retry
from requests.adapters import HTTPAdapter

class EnhancedWebCrawler:
    def __init__(self, start_url, crawl_mode="Standard"):
        self.session = self._create_session()
        self.start_url = start_url
        self.keywords = ["gowithguide", "go with guide", "go-with-guide", "87121"]
        self.main_domain = urlparse(start_url).netloc
        self.crawl_mode = crawl_mode
        self.max_pages = {"Quick": 5, "Standard": 150, "Complete": 1500}[crawl_mode]
        self.visited = set()
        self.results = []
        self.queue = deque([start_url])
        self.categories = []
        self.current_category = None
        self.status_messages = []
        self.user_stopped = False
        self.pages_crawled = 0
        self.redirect_cache = {}
        self.internal_links = set()
        self.known_shorteners = [
            'bit.ly', 'tinyurl.com', 'goo.gl', 't.co', 'ow.ly', 'is.gd', 
            'buff.ly', 'adf.ly', 'bit.do', 'mcaf.ee', 'su.pr', 'tiny.cc',
            'tidd.ly', 'redirectingat.com', 'go.redirectingat.com', 'go.skimresources.com'
        ]
        self.awin_domains = ['awin1.com', 'zenaps.com']
        self.potential_affiliate_domains = [
            'track.', 'go.', 'click.', 'buy.', 'shop.', 'link.', 'visit.',
            'affiliate.', 'partners.', 'tracking.', 'redirect.', 'ref.'
        ]
        self.crawled_pages_content = {}
        self.url_fragments_checked = set()
        self.setup_logger()

    def setup_logger(self):
        self.logger = logging.getLogger('crawler')
        self.logger.setLevel(logging.INFO)
        if not self.logger.handlers:
            handler = logging.StreamHandler()
            formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
            handler.setFormatter(formatter)
            self.logger.addHandler(handler)

    def _create_session(self):
        session = requests.Session()
        retries = Retry(
            total=3,
            backoff_factor=0.5,
            status_forcelist=[429, 500, 502, 503, 504],
            allowed_methods=["GET", "HEAD"]
        )
        adapter = HTTPAdapter(max_retries=retries)
        session.mount("http://", adapter)
        session.mount("https://", adapter)
        session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8',
            'Accept-Language': 'en-US,en;q=0.5',
            'Connection': 'keep-alive',
            'Upgrade-Insecure-Requests': '1',
            'Cache-Control': 'max-age=0'
        })
        return session

    def is_same_domain(self, url):
        """Check if URL is from the same domain or subdomain as the start URL."""
        main_domain_parts = tldextract.extract(self.start_url)
        url_domain_parts = tldextract.extract(url)
        return (main_domain_parts.domain == url_domain_parts.domain and 
                main_domain_parts.suffix == url_domain_parts.suffix)

    def is_subdomain_of(self, url_netloc):
        """Check if URL netloc is a subdomain of the main domain."""
        main_domain = self.main_domain.replace("www.", "").lower()
        url_netloc = url_netloc.replace("www.", "").lower()
        return url_netloc.endswith("." + main_domain) or url_netloc == main_domain

    def is_relevant_path(self, url):
        """Check if URL path is relevant for crawling based on patterns and extensions."""
        parsed_url = urlparse(url)
        path = parsed_url.path.lower()
        
        # Skip certain file types
        if re.search(r'\.(jpg|jpeg|png|gif|svg|pdf|zip|rar|css|js|xml|json)$', path):
            return False
            
        # Skip typical non-content pages
        if re.search(r'/(login|logout|register|signin|signout|cart|checkout|privacy|terms)/?$', path):
            return False
            
        # Prioritize potentially content-rich pages
        if re.search(r'/(post|article|blog|news|story|travel|guide|destination)/', path):
            return True
            
        # Avoid parameter-heavy URLs which might be pagination or filters
        if len(parse_qs(parsed_url.query)) > 3:
            return False
            
        return True

    def normalize_url(self, url):
        """Normalize URL to avoid crawling duplicates."""
        parsed = urlparse(url)
        # Remove fragments
        normalized = urlunparse((parsed.scheme, parsed.netloc, parsed.path, 
                                parsed.params, parsed.query, ''))
        # Remove trailing slash
        if normalized.endswith('/'):
            normalized = normalized[:-1]
        return normalized

    def looks_like_affiliate_url(self, url):
        """Check if URL looks like an affiliate URL based on domain and parameter patterns."""
        url_lower = url.lower()
        parsed_url = urlparse(url_lower)
        netloc = parsed_url.netloc
        
        # Check for known URL shorteners
        if any(shortener in netloc for shortener in self.known_shorteners):
            return True
            
        # Check for potential affiliate domains
        if any(tracker in netloc for tracker in self.potential_affiliate_domains):
            return True
            
        # Check for AWIN domains only if '87121' is in the URL
        if any(domain in netloc for domain in self.awin_domains) and '87121' in url_lower:
            return True
            
        # Check for common affiliate parameters
        query_params = parse_qs(parsed_url.query)
        affiliate_params = ['aff', 'affid', 'affiliateid', 'ref', 'refid', 'referral', 
                           'referralid', 'partner', 'partnerId', 'utm_source']
        
        for param in affiliate_params:
            if param in query_params:
                return True
                
        # Check for multiple tracking parameters
        tracking_params = ['utm_', 'ref', 'aff', 'source', 'campaign', 'medium']
        tracking_count = sum(1 for param in query_params if any(t in param for t in tracking_params))
        if tracking_count >= 2:
            return True
            
        return False

    def extract_redirection_url(self, html_content, url):
        """Extract URLs from redirect patterns in HTML and JavaScript."""
        redirect_urls = []
        
        # Look for meta refresh tags
        soup = BeautifulSoup(html_content, 'lxml')
        meta_refresh = soup.find('meta', attrs={'http-equiv': re.compile('^refresh$', re.I)})
        if meta_refresh and meta_refresh.get('content'):
            match = re.search(r'url=(.+)', meta_refresh['content'], re.I)
            if match:
                redirect_url = match.group(1).strip()
                redirect_urls.append(urljoin(url, redirect_url))
        
        # Look for JavaScript redirects
        script_patterns = [
            r'window\.location(?:\.href)?\s*=\s*[\'"](.+?)[\'"]',
            r'window\.location\.replace\([\'"](.+?)[\'"]\)',
            r'window\.open\([\'"](.+?)[\'"]\)',
            r'location\.href\s*=\s*[\'"](.+?)[\'"]',
            r'location\.replace\([\'"](.+?)[\'"]\)',
            r'setTimeout\([\'"]window\.location\.href=[\'"](.+?)[\'"][\'"]',
            r'url:\s*[\'"](.+?)[\'"]',
            r'href=[\'"](.+?)[\'"]'
        ]
        
        scripts = soup.find_all('script')
        for script in scripts:
            if script.string:
                for pattern in script_patterns:
                    matches = re.findall(pattern, script.string)
                    for match in matches:
                        if len(match) > 10:  # Avoid capturing small fragments
                            redirect_urls.append(urljoin(url, match))
        
        # Look for redirect_to parameters
        parsed_url = urlparse(url)
        query_params = parse_qs(parsed_url.query)
        redirect_params = ['redirect_to', 'redirect', 'url', 'link', 'goto', 'target']
        
        for param in redirect_params:
            if param in query_params:
                redirect_urls.append(urljoin(url, query_params[param][0]))
                
        return redirect_urls

    def extract_urls_from_onclick(self, element, source_url):
        """Extract URLs from onclick attributes."""
        if element.has_attr('onclick'):
            onclick = element['onclick']
            url_matches = re.findall(r'(?:window\.open|location\.href|window\.location)\s*=\s*[\'"](.+?)[\'"]', onclick)
            for url_match in url_matches:
                if url_match.startswith('http') or url_match.startswith('/'):
                    yield urljoin(source_url, url_match)

    def resolve_redirects(self, url):
        """Resolve URL redirects and cache the results."""
        if url in self.redirect_cache:
            return self.redirect_cache[url]
            
        try:
            parsed = urlparse(url)
            
            # Skip non-HTTP URLs
            if parsed.scheme not in ('http', 'https'):
                return url, []
                
            # Handle known URL shorteners with extra care
            is_shortener = any(domain in parsed.netloc for domain in self.known_shorteners)
            
            # For shorteners and potential affiliate URLs, use GET instead of HEAD
            if is_shortener or self.looks_like_affiliate_url(url):
                response = self.session.get(
                    url, 
                    allow_redirects=True, 
                    timeout=15,
                    headers={
                        'User-Agent': 'Mozilla/5.0',
                        'Accept': 'text/html,application/xhtml+xml'
                    }
                )
            else:
                # Use HEAD for efficiency on regular URLs
                response = self.session.head(
                    url, 
                    allow_redirects=True, 
                    timeout=10
                )
                
            final_url = response.url
            history = [r.url for r in response.history]
            
            # For certain URLs, extract redirects from page content (JavaScript redirects)
            if is_shortener and response.status_code == 200 and 'text/html' in response.headers.get('Content-Type', ''):
                potential_redirects = self.extract_redirection_url(response.text, url)
                if potential_redirects:
                    history.append(final_url)
                    final_url = potential_redirects[0]
            
            # Some services use 200 status but redirect via JavaScript or meta tags
            if not history and url != final_url:
                history = [url]
            
            # Handle cases where HEAD doesn't show redirects but GET would
            if not history and response.status_code == 200 and not is_shortener:
                try:
                    response_get = self.session.get(url, allow_redirects=False, timeout=10)
                    if 300 <= response_get.status_code < 400:
                        location = response_get.headers.get('Location', '')
                        if location:
                            history = [url]
                            final_url = urljoin(url, location)
                except Exception:
                    pass
                    
            self.redirect_cache[url] = (final_url, history)
            return final_url, history
            
        except Exception as e:
            self.status_messages.append(f"Error resolving redirects for {url}: {str(e)}")
            return url, []

    def get_matched_keywords(self, text):
        """Find keywords in the given text using improved pattern matching."""
        if not isinstance(text, str) or not text.strip():
            return []
            
        text_lower = text.lower().strip()
        exact_matches = []
        
        # Check for exact keyword matches with word boundary consideration
        for kw in self.keywords:
            kw_lower = kw.lower()
            pattern = rf'(?:^|\s|[-_/=&]){re.escape(kw_lower)}(?:$|\s|[-_/=&])'
            if re.search(pattern, text_lower):
                exact_matches.append(kw)
            
            # Handle URL-encoded keywords
            kw_encoded = kw.replace(' ', '%20')
            pattern_encoded = rf'(?:^|\s|[-_/=&]){re.escape(kw_encoded)}(?:$|\s|[-_/=&])'
            if re.search(pattern_encoded, text_lower):
                exact_matches.append(kw)
                
            # Handle plus-encoded keywords
            kw_plus_encoded = kw.replace(' ', '+')
            pattern_plus_encoded = rf'(?:^|\s|[-_/=&]){re.escape(kw_plus_encoded)}(?:$|\s|[-_/=&])'
            if re.search(pattern_plus_encoded, text_lower):
                exact_matches.append(kw)
        
        # Check for specific URL patterns that indicate affiliate links
        url_patterns = [
            r'(?:https?://)?(?:www\.)?gowithguide\.com',
            r'utm_source=([^&]*)',
            r'utm_campaign=([^&]*)',
            r'sv1=([^&]*)',
            r'awc=([^&]*)',
            r'87121(?:_\d+|%5F\d+)?',
            r'awin\d\.com',
            r'awinmid=\d+',
            r'awinaffid=\d+'
        ]
        
        for pattern in url_patterns:
            matches = re.findall(pattern, text_lower)
            for match in matches:
                if isinstance(match, str):
                    for kw in self.keywords:
                        if kw.lower() in match.lower():
                            exact_matches.append(kw)
                        # Only add if the match contains '87121' or 'gowithguide'
                        elif '87121' in match.lower() or 'gowithguide' in match.lower():
                            exact_matches.append(kw)
        
        return list(set(exact_matches))

    def check_url_for_keywords(self, url, source_url):
        """Check if URL contains keywords or redirects to URLs with keywords."""
        if not url or not isinstance(url, str):
            return
            
        # Skip checking already processed URL fragments
        url_hash = hashlib.md5(url.encode()).hexdigest()
        if url_hash in self.url_fragments_checked:
            return
        self.url_fragments_checked.add(url_hash)
        
        # Check if URL directly contains keywords
        matched_kws = self.get_matched_keywords(url)
        if matched_kws:
            self.add_result(
                source_url=source_url,
                matched_url=url,
                element='url',
                attribute='href',
                content=url,
                keywords=matched_kws,
                location_type='direct_url'
            )
            
        # Check if URL looks like an affiliate link
        if self.looks_like_affiliate_url(url):
            # For all links that match affiliate patterns, resolve redirects
            final_url, history = self.resolve_redirects(url)
            
            # Check final URL for keywords
            if final_url != url:
                matched_kws_final = self.get_matched_keywords(final_url)
                if matched_kws_final:
                    self.add_result(
                        source_url=source_url,
                        matched_url=final_url,
                        element='url',
                        attribute='href',
                        content=f"Redirected from: {url} to: {final_url}",
                        keywords=matched_kws_final,
                        location_type='redirected_url'
                    )
                # Additional check for AWIN links
                elif any(domain in final_url for domain in self.awin_domains):
                    # Parse AWIN parameters
                    parsed = urlparse(final_url)
                    params = parse_qs(parsed.query)
                    
                    # Look for AWIN merchant ID
                    awin_mid = None
                    if 'awinmid' in params:
                        awin_mid = params['awinmid'][0]
                    elif 'v' in params:  # Some AWIN links use 'v' for merchant ID
                        awin_mid = params['v'][0]
                        
                    # Check if the merchant ID matches our keyword
                    if awin_mid == '87121':
                        self.add_result(
                            source_url=source_url,
                            matched_url=final_url,
                            element='url',
                            attribute='href',
                            content=f"AWIN link with merchant ID 87121: {final_url}",
                            keywords=['87121'],
                            location_type='awin_affiliate_url'
                        )
            
            # Check each intermediate URL in redirect chain
            for intermediate_url in history:
                matched_kws_intermediate = self.get_matched_keywords(intermediate_url)
                if matched_kws_intermediate:
                    self.add_result(
                        source_url=source_url,
                        matched_url=intermediate_url,
                        element='url',
                        attribute='href',
                        content=f"Redirect chain URL: {intermediate_url}",
                        keywords=matched_kws_intermediate,
                        location_type='redirect_chain_url'
                    )
                # Additional check for AWIN links in redirect chain
                elif any(domain in intermediate_url for domain in self.awin_domains):
                    parsed = urlparse(intermediate_url)
                    params = parse_qs(parsed.query)
                    if 'awinmid' in params and params['awinmid'][0] == '87121':
                        self.add_result(
                            source_url=source_url,
                            matched_url=intermediate_url,
                            element='url',
                            attribute='href',
                            content=f"AWIN redirect link with merchant ID 87121: {intermediate_url}",
                            keywords=['87121'],
                            location_type='awin_affiliate_redirect'
                        )

    def process_url(self, url):
        """Process a URL by crawling it and checking for affiliate links."""
        if url in self.visited or self.pages_crawled >= self.max_pages or not url:
            return []
            
        self.visited.add(url)
        self.pages_crawled += 1
        
        try:
            response = self.session.get(
                url, 
                headers={
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
                    'Accept': 'text/html,application/xhtml+xml,application/xml'
                }, 
                timeout=20, 
                allow_redirects=True
            )
            response.raise_for_status()
        except Exception as e:
            self.status_messages.append(f"Error fetching {url}: {str(e)}")
            return []
            
        # Skip non-HTML content
        content_type = response.headers.get('Content-Type', '').lower()
        if 'text/html' not in content_type and 'application/xhtml+xml' not in content_type:
            return []
            
        final_url = response.url
        html_content = response.text
        
        # Cache page content for potential reuse
        self.crawled_pages_content[final_url] = html_content
        
        # Parse with BeautifulSoup
        soup = BeautifulSoup(html_content, 'lxml')
        
        # Check for JavaScript redirects
        js_redirects = self.extract_redirection_url(html_content, final_url)
        for js_redirect in js_redirects:
            self.check_url_for_keywords(js_redirect, final_url)
        
        # Get all interesting elements to check
        elements = soup.find_all([
            'a', 'div', 'section', 'title', 'main', 
            'article', 'span', 'p', 'img', 'meta', 
            'iframe', 'script', 'button', 'form'
        ])
        
        internal_urls = []
        
        # Process each element
        for element in elements:
            urls = self.check_element(element, final_url)
            internal_urls.extend(urls)
        
        # Extract URLs from JavaScript
        script_tags = soup.find_all('script')
        for script in script_tags:
            if script.string:
                # Find direct URLs in JavaScript
                urls_in_js = re.findall(r'(https?://[^\s\'"]+)', script.string)
                for js_url in urls_in_js:
                    # Clean URL if it has quotes or other characters at the end
                    js_url = re.sub(r'["\')]$', '', js_url)
                    self.check_url_for_keywords(js_url, final_url)
                    parsed_js_url = urlparse(js_url)
                    if self.is_subdomain_of(parsed_js_url.netloc):
                        internal_urls.append(js_url)
                
                # Look for JSON-like data in JavaScript that might contain URLs
                json_patterns = [
                    r'["\']?(?:url|href|link)["\']?\s*:\s*["\']?(https?://[^\s\'"]+)["\']?',
                    r'window\.location\s*=\s*["\']?(https?://[^\s\'"]+)["\']?',
                    r'["\']?(?:redirectUrl|redirect_url|redirectLink)["\']?\s*:\s*["\']?(https?://[^\s\'"]+)["\']?',
                    r'["\']?(?:affiliateUrl|affiliate_url|partnerUrl)["\']?\s*:\s*["\']?(https?://[^\s\'"]+)["\']?'
                ]
                
                for pattern in json_patterns:
                    matches = re.findall(pattern, script.string)
                    for match in matches:
                        # Clean up the URL
                        match = re.sub(r'["\')]$', '', match)
                        self.check_url_for_keywords(match, final_url)
                        if self.is_subdomain_of(urlparse(match).netloc):
                            internal_urls.append(match)
        
        # Extract all links from data attributes that might contain URLs
        for element in soup.find_all(attrs=re.compile(r"^data-.*")):
            for attr_name, attr_value in element.attrs.items():
                if attr_name.startswith('data-') and isinstance(attr_value, str):
                    # Look for URL-like strings in data attributes
                    if ('url' in attr_name.lower() or 'link' in attr_name.lower() or 
                        'href' in attr_name.lower() or 'src' in attr_name.lower()):
                        if attr_value.startswith(('http://', 'https://', '//')):
                            full_url = urljoin(final_url, attr_value)
                            self.check_url_for_keywords(full_url, final_url)
                            if self.is_subdomain_of(urlparse(full_url).netloc):
                                internal_urls.append(full_url)
        
        # Check for links in structured data
        for script in soup.find_all('script', {'type': 'application/ld+json'}):
            if script.string:
                try:
                    json_data = json.loads(script.string)
                    self._extract_urls_from_json(json_data, final_url, internal_urls)
                except json.JSONDecodeError:
                    pass
                    
        # Deduplicate and filter internal URLs
        filtered_internal_urls = []
        seen_urls = set()
        
        for url in internal_urls:
            # Normalize URL to avoid duplicates
            normalized_url = self.normalize_url(url)
            if normalized_url not in seen_urls and normalized_url not in self.visited:
                seen_urls.add(normalized_url)
                if self.is_relevant_path(normalized_url):
                    filtered_internal_urls.append(url)
                    
        return filtered_internal_urls

    def _extract_urls_from_json(self, json_data, base_url, url_list):
        """Recursively extract URLs from JSON data."""
        if isinstance(json_data, dict):
            for key, value in json_data.items():
                if key.lower() in ('url', 'link', 'href', 'src') and isinstance(value, str):
                    if value.startswith(('http', '/')):
                        full_url = urljoin(base_url, value)
                        self.check_url_for_keywords(full_url, base_url)
                        if self.is_subdomain_of(urlparse(full_url).netloc):
                            url_list.append(full_url)
                else:
                    self._extract_urls_from_json(value, base_url, url_list)
        elif isinstance(json_data, list):
            for item in json_data:
                self._extract_urls_from_json(item, base_url, url_list)

    def check_element(self, element, source_url):
        """Check an HTML element for affiliate links and extract internal URLs."""
        internal_urls = []
        element_type = element.name if element.name else 'unknown'
        
        # Process anchor elements (links)
        if element.name == 'a':
            # Check href attribute for direct affiliate links
            if element.has_attr('href'):
                href = element['href'].strip()
                if href:
                    # Skip javascript: and mailto: links
                    if not href.startswith(('javascript:', 'mailto:', 'tel:')):
                        resolved_url = urljoin(source_url, href)
                        self.check_url_for_keywords(resolved_url, source_url)
                        
                        # Check text content of link for keywords
                        text = element.get_text(separator=' ', strip=True)
                        matched_kws = self.get_matched_keywords(text)
                        if matched_kws:
                            self.add_result(
                                source_url=source_url,
                                matched_url=resolved_url,
                                element=element_type,
                                attribute='text',
                                content=text,
                                keywords=matched_kws,
                                location_type='anchor_text'
                            )
                            
                        # Add to internal URLs if from same domain
                        parsed_url = urlparse(resolved_url)
                        if self.is_subdomain_of(parsed_url.netloc):
                            internal_urls.append(resolved_url)
            
            # Check for image banners
            img = element.find('img')
            if img:
                # Check image alt text for keywords
                if img.get('alt'):
                    alt_text = img['alt'].strip()
                    matched_kws = self.get_matched_keywords(alt_text)
                    if matched_kws and element.has_attr('href'):
                        resolved_url = urljoin(source_url, element['href'].strip())
                        self.add_result(
                            source_url=source_url,
                            matched_url=resolved_url,
                            element='a',
                            attribute='img_alt',
                            content=alt_text,
                            keywords=matched_kws,
                            location_type='image_banner'
                        )
                
                # Check image title for keywords
                if img.get('title'):
                    title_text = img['title'].strip()
                    matched_kws = self.get_matched_keywords(title_text)
                    if matched_kws and element.has_attr('href'):
                        resolved_url = urljoin(source_url, element['href'].strip())
                        self.add_result(
                            source_url=source_url,
                            matched_url=resolved_url,
                            element='a',
                            attribute='img_title',
                            content=title_text,
                            keywords=matched_kws,
                            location_type='image_banner'
                        )
                        
                # Check image src for affiliate patterns
                if img.get('src'):
                    img_src = img['src'].strip()
                    if self.looks_like_affiliate_url(img_src):
                        img_url = urljoin(source_url, img_src)
                        self.check_url_for_keywords(img_url, source_url)
            
            # Check for onclick attributes with URLs
            for onclick_url in self.extract_urls_from_onclick(element, source_url):
                self.check_url_for_keywords(onclick_url, source_url)
                parsed_onclick_url = urlparse(onclick_url)
                if self.is_subdomain_of(parsed_onclick_url.netloc):
                    internal_urls.append(onclick_url)
                    
            # Check all data attributes for potential affiliate links
            for attr_name, attr_val in element.attrs.items():
                if attr_name.startswith('data-') and isinstance(attr_val, str):
                    if ('url' in attr_name or 'link' in attr_name or 'href' in attr_name):
                        if attr_val.startswith(('http', '/')):
                            data_url = urljoin(source_url, attr_val)
                            self.check_url_for_keywords(data_url, source_url)
                            if self.is_subdomain_of(urlparse(data_url).netloc):
                                internal_urls.append(data_url)
        
        # Check text content elements for keywords
        if element.name in ['p', 'div', 'span', 'title', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6']:
            text = element.get_text(separator=' ', strip=True)
            matched_kws = self.get_matched_keywords(text)
            if matched_kws:
                self.add_result(
                    source_url=source_url,
                    matched_url=source_url,
                    element=element_type,
                    attribute='text',
                    content=text,
                    keywords=matched_kws,
                    location_type='content'
                )
            
            # Extract URLs from text content
            url_matches = re.findall(r'https?://[^\s\'"<>]+', text)
            for url_match in url_matches:
                # Clean up URL
                url_match = re.sub(r'[,.:;!?)]$', '', url_match)
                self.check_url_for_keywords(url_match, source_url)
        
        # Check meta tags
        if element.name == 'meta' and element.get('content'):
            content = element['content'].strip()
            matched_kws = self.get_matched_keywords(content)
            if matched_kws:
                attr_name = element.get('name') or element.get('property') or 'meta'
                self.add_result(
                    source_url=source_url,
                    matched_url=source_url,
                    element=element_type,
                    attribute=attr_name,
                    content=content,
                    keywords=matched_kws,
                    location_type='meta'
                )
            
            # Check for URLs in meta content
            if ('url' in element.get('name', '').lower() or 
                'url' in element.get('property', '').lower()):
                if content.startswith(('http', '/')):
                    meta_url = urljoin(source_url, content)
                    self.check_url_for_keywords(meta_url, source_url)
                    if self.is_subdomain_of(urlparse(meta_url).netloc):
                        internal_urls.append(meta_url)
        
        # Check images for affiliate links in alt/title text
        if element.name == 'img':
            # Alt text check
            if element.get('alt'):
                alt_text = element['alt'].strip()
                matched_kws = self.get_matched_keywords(alt_text)
                if matched_kws:
                    self.add_result(
                        source_url=source_url,
                        matched_url=source_url,
                        element=element_type,
                        attribute='alt',
                        content=alt_text,
                        keywords=matched_kws,
                        location_type='alt_text'
                    )
            
            # Title text check
            if element.get('title'):
                title_text = element['title'].strip()
                matched_kws = self.get_matched_keywords(title_text)
                if matched_kws:
                    self.add_result(
                        source_url=source_url,
                        matched_url=source_url,
                        element=element_type,
                        attribute='title',
                        content=title_text,
                        keywords=matched_kws,
                        location_type='title_text'
                    )
        
        # Check iframes for affiliate content
        if element.name == 'iframe' and element.get('src'):
            iframe_src = element['src'].strip()
            if iframe_src.startswith(('http', '//')):
                iframe_url = urljoin(source_url, iframe_src)
                self.check_url_for_keywords(iframe_url, source_url)
        
        # Check button elements which might trigger affiliate links
        if element.name == 'button':
            # Check for onclick handlers that might contain URLs
            for onclick_url in self.extract_urls_from_onclick(element, source_url):
                self.check_url_for_keywords(onclick_url, source_url)
                
            # Check text content for keywords
            button_text = element.get_text(separator=' ', strip=True)
            matched_kws = self.get_matched_keywords(button_text)
            if matched_kws:
                self.add_result(
                    source_url=source_url,
                    matched_url=source_url,
                    element=element_type,
                    attribute='text',
                    content=button_text,
                    keywords=matched_kws,
                    location_type='button_text'
                )
        
        # Check data attributes for URLs or affiliate parameters
        for attr in element.attrs:
            if attr.startswith('data-') and isinstance(element[attr], str):
                attr_value = element[attr].strip()
                
                # Look for URL-like data attributes
                if ('url' in attr.lower() or 'href' in attr.lower() or 'link' in attr.lower()):
                    if attr_value and (attr_value.startswith(('http', '//'))):
                        data_url = urljoin(source_url, attr_value)
                        self.check_url_for_keywords(data_url, source_url)
                        if self.is_subdomain_of(urlparse(data_url).netloc):
                            internal_urls.append(data_url)
                
                # Check all data attributes for affiliate keywords
                matched_kws = self.get_matched_keywords(attr_value)
                if matched_kws:
                    self.add_result(
                        source_url=source_url,
                        matched_url=source_url,
                        element=element_type,
                        attribute=attr,
                        content=attr_value,
                        keywords=matched_kws,
                        location_type='data_attribute'
                    )
                    
        return internal_urls

    def add_result(self, source_url, matched_url, element, attribute, content, keywords, location_type):
        """Add a new result to the results list, avoiding duplicates."""
        for keyword in keywords:
            # Create a unique identifier for this match
            match_id = hashlib.md5(f"{matched_url}:{element}:{attribute}:{keyword}:{location_type}".encode()).hexdigest()
            
            # Check if this exact match is already in results
            if any(result.get('match_id') == match_id for result in self.results):
                continue
                
            result = {
                'source_url': source_url,
                'matched_url': matched_url,
                'element': element,
                'attribute': attribute,
                'keyword': keyword,
                'content': content[:500] if content else '',
                'location_type': location_type,
                'timestamp': datetime.datetime.now().isoformat(),
                'match_id': match_id
            }
            
            self.results.append(result)
            self.logger.info(f"Found affiliate link: {matched_url} (keyword: {keyword})")

    def extract_categories(self):
        """Extract categories from the website to guide crawling."""
        try:
            response = self.session.get(self.start_url)
            soup = BeautifulSoup(response.text, 'lxml')
            categories = []
            
            # Extend category priority to cover more common content sections
            category_priority = [
                'travel', 'blog', 'resources', 'guides', 'destinations',
                'tours', 'activities', 'affiliate', 'partner', 'reviews',
                'articles', 'news', 'features', 'stories'
            ]
            
            # Find navigation menus which often contain categories
            nav_elements = soup.find_all(['nav', 'ul', 'div'], class_=lambda c: c and any(
                term in c.lower() for term in ['nav', 'menu', 'categories', 'main-menu']
            ))
            
            for nav in nav_elements:
                for link in nav.find_all('a', href=True):
                    href = link['href'].lower()
                    text = link.get_text().lower().strip()
                    
                    # Skip empty links and fragment links
                    if not href or href.startswith('#'):
                        continue
                        
                    # Skip likely non-content pages
                    if any(term in href for term in ['/cart', '/login', '/register', '/account']):
                        continue
                    
                    full_url = urljoin(self.start_url, href)
                    
                    # Skip external links
                    if not self.is_same_domain(full_url):
                        continue
                    
                    # Determine category name
                    cat_name = None
                    
                    # Check for structured category paths
                    cat_match = re.search(r'/(?:category|topics|sections?|tags?)/([^/]+)', href)
                    if cat_match:
                        cat_name = cat_match.group(1).lower()
                    else:
                        # Try to find a category name from link text or URL
                        for cat in category_priority:
                            if cat in href or cat in text:
                                cat_name = cat
                                break
                    
                    if not cat_name:
                        # Use link text if it's short and likely a category name
                        if 3 <= len(text) <= 20 and ' ' not in text:
                            cat_name = text
                        else:
                            # Extract last path segment
                            path_parts = urlparse(full_url).path.strip('/').split('/')
                            if path_parts:
                                cat_name = path_parts[-1].lower()
                            else:
                                cat_name = 'other'
                    
                    categories.append((cat_name, full_url))
            
            # Sort categories by priority
            sorted_categories = []
            for cat in category_priority:
                matched = [c for c in categories if c[0] == cat]
                if matched:
                    sorted_categories.append(matched[0])
            
            # Add remaining categories
            remaining = [c for c in categories if c[0] not in [sc[0] for sc in sorted_categories]]
            sorted_categories.extend(remaining)
            
            # Return unique categories, limited to 10
            unique_cat_urls = set()
            unique_categories = []
            
            for cat_name, cat_url in sorted_categories:
                if cat_url not in unique_cat_urls:
                    unique_cat_urls.add(cat_url)
                    unique_categories.append((cat_name, cat_url))
                    if len(unique_categories) >= 10:
                        break
                        
            return unique_categories
        except Exception as e:
            self.status_messages.append(f"Error extracting categories: {str(e)}")
            return []

    def get_main_pages(self):
        """Get main pages from website homepage for crawling."""
        try:
            response = self.session.get(self.start_url)
            soup = BeautifulSoup(response.text, 'lxml')
            main_links = []
            seen_urls = set()
            
            # Priority content patterns that might contain affiliate links
            content_patterns = [
                r'/(?:post|article|blog|story|guide)s?/',
                r'/(?:travel|destination|tour)s?/',
                r'/(?:partner|affiliate)s?/',
                r'/(?:review|resource)s?/'
            ]
            
            # Prioritize links with these keywords in text or URL
            priority_terms = [
                'affiliate', 'partner', 'sponsor', 'advertis', 
                'review', 'guid', 'tour', 'travel', 'destination'
            ]
            
            # Extract all links from the page
            all_links = []
            for link in soup.find_all('a', href=True):
                href = link['href'].strip()
                if not href or href.startswith(('#', 'javascript:', 'mailto:', 'tel:')):
                    continue
                    
                url = urljoin(self.start_url, href)
                
                # Only keep internal links
                if not self.is_same_domain(url):
                    continue
                    
                # Skip links to files
                if re.search(r'\.(jpg|jpeg|png|gif|pdf|zip|doc|docx)$', url, re.I):
                    continue
                
                text = link.get_text().strip().lower()
                priority = 0
                
                # Assign priority to links
                for pattern in content_patterns:
                    if re.search(pattern, url, re.I):
                        priority += 3
                        
                for term in priority_terms:
                    if term in url.lower() or term in text:
                        priority += 2
                
                # Higher priority for links from article sections
                parent = link.find_parent(['article', 'section', 'main'])
                if parent:
                    priority += 1
                
                all_links.append((url, priority))
            
            # Sort by priority and deduplicate
            all_links.sort(key=lambda x: x[1], reverse=True)
            
            for url, _ in all_links:
                normalized_url = self.normalize_url(url)
                if normalized_url not in seen_urls and self.is_relevant_path(normalized_url):
                    seen_urls.add(normalized_url)
                    main_links.append(url)
                    if len(main_links) >= self.max_pages:
                        break
                        
            return main_links
        except Exception as e:
            self.status_messages.append(f"Error getting main pages: {str(e)}")
            return []

    def get_category_pages(self, category_url):
        """Get pages from a specific category for crawling."""
        try:
            response = self.session.get(category_url)
            soup = BeautifulSoup(response.text, 'lxml')
            article_links = []
            seen_urls = set()
            
            # First, look for article containers
            article_elements = soup.find_all(['article', 'div', 'section', 'li'], class_=lambda c: c and any(
                term in (c.lower() if c else '') for term in ['post', 'article', 'entry', 'item', 'card']
            ))
            
            # If found, extract links from these containers first
            if article_elements:
                for container in article_elements:
                    links = container.find_all('a', href=True)
                    for link in links:
                        url = urljoin(category_url, link['href'].strip())
                        
                        # Skip non-content URLs
                        if not self.is_same_domain(url) or not self.is_relevant_path(url):
                            continue
                            
                        normalized_url = self.normalize_url(url)
                        if normalized_url not in seen_urls:
                            seen_urls.add(normalized_url)
                            article_links.append(url)
            
            # If not enough links found, get all links from the page
            if len(article_links) < self.max_pages:
                for link in soup.find_all('a', href=True):
                    url = urljoin(category_url, link['href'].strip())
                    
                    # Skip already found links
                    normalized_url = self.normalize_url(url)
                    if normalized_url in seen_urls:
                        continue
                        
                    # Only keep internal content links
                    if not self.is_same_domain(url) or not self.is_relevant_path(url):
                        continue
                        
                    # Prioritize likely content pages
                    if (re.search(r'/(?:article|post|blog|news|story|guide)/', url) or
                        re.search(r'/\d{4}/\d{2}/', url)):
                        seen_urls.add(normalized_url)
                        article_links.append(url)
                        if len(article_links) >= self.max_pages:
                            break
            
            # Try to sort by date if possible
            try:
                date_sorted_links = []
                for url in article_links:
                    date_match = re.search(r'/(\d{4})/(\d{2})/', url)
                    if date_match:
                        year, month = date_match.groups()
                        date_sorted_links.append((url, (int(year), int(month))))
                
                if date_sorted_links:
                    date_sorted_links.sort(key=lambda x: x[1], reverse=True)
                    article_links = [url for url, _ in date_sorted_links]
            except Exception:
                pass
                
            return article_links[:self.max_pages]
        except Exception as e:
            self.status_messages.append(f"Error getting category pages: {str(e)}")
            return []

def generate_csv(results):
    """Generate CSV file from crawl results."""
    csv_file = StringIO()
    writer = csv.DictWriter(csv_file, fieldnames=[
        'source_url', 'matched_url', 'keyword', 
        'location_type', 'element', 'attribute',
        'content_sample', 'timestamp'
    ])
    writer.writeheader()
    for result in results:
        writer.writerow({
            'source_url': result['source_url'],
            'matched_url': result['matched_url'],
            'keyword': result['keyword'],
            'location_type': result['location_type'],
            'element': result['element'],
            'attribute': result['attribute'],
            'content_sample': result['content'][:300] if result['content'] else '',
            'timestamp': result['timestamp']
        })
    return csv_file.getvalue()

def main():
    st.set_page_config(page_title="Enhanced Web Crawler", page_icon="🌐", layout="wide")
    
    # JavaScript Keep-Alive Mechanism
    st.markdown("""
        <script>
            // Keep-alive mechanism
            function keepAlive() {
                fetch(window.location.href, {
                    method: 'GET',
                    headers: {
                        'Content-Type': 'application/json',
                        'Cache-Control': 'no-cache'
                    },
                    keepalive: true
                });
            }
            
            // Send keep-alive every 30 seconds
            setInterval(keepAlive, 30000);
            
            // Prevent browser throttling
            let activityInterval = setInterval(() => {
                document.dispatchEvent(new Event('mousemove'));
            }, 60000);
            
            // Cleanup on page unload
            window.addEventListener('beforeunload', () => {
                clearInterval(activityInterval);
            });
        </script>
    """, unsafe_allow_html=True)

    # Material UI-inspired CSS with enhanced color scheme
    st.markdown("""
        <style>
        :root {
            --primary-color: #1976D2;
            --primary-light: #42a5f5;
            --primary-dark: #1565c0;
            --secondary-color: #26a69a;
            --background-color: #f5f7fa;
            --card-color: #ffffff;
            --text-color: #212121;
            --text-light: #757575;
            --error-color: #f44336;
            --success-color: #4caf50;
            --warning-color: #ff9800;
            --info-color: #2196f3;
        }
        
        body {
            background-color: var(--background-color);
            color: var(--text-color);
            font-family: 'Roboto', sans-serif;
        }
        
        .main-header {
            color: var(--primary-color);
            font-weight: 500;
            margin-bottom: 1rem;
            padding-bottom: 0.5rem;
            border-bottom: 2px solid var(--primary-light);
        }
        
        .subheader {
            color: var(--primary-dark);
            font-weight: 400;
            margin-top: 1.5rem;
            margin-bottom: 0.75rem;
        }
        
        .stButton>button {
            background-color: var(--primary-color);
            color: white;
            border-radius: 4px;
            border: none;
            padding: 0.5rem 1rem;
            font-weight: 500;
            transition: background-color 0.3s;
        }
        
        .stButton>button:hover {
            background-color: var(--primary-dark);
        }
        
        .stTextInput>div>input {
            background-color: var(--card-color);
            border: 1px solid #e0e0e0;
            border-radius: 4px;
            padding: 0.5rem;
            font-size: 1rem;
        }
        
        .stSelectbox>div>div>div {
            background-color: var(--card-color);
            border: 1px solid #e0e0e0;
        }
        
        .status-box {
            background-color: #e3f2fd;
            color: var(--primary-dark);
            padding: 1rem;
            border-radius: 4px;
            border-left: 4px solid var(--primary-color);
            margin-bottom: 1rem;
            box-shadow: 0 2px 5px rgba(0,0,0,0.05);
        }
        
        .results-box {
            background-color: var(--card-color);
            padding: 1.5rem;
            border-radius: 4px;
            margin-bottom: 1.5rem;
            box-shadow: 0 2px 8px rgba(0,0,0,0.08);
        }
        
        .match-item {
            padding: 1rem;
            margin-bottom: 1rem;
            border-radius: 4px;
            border-left: 4px solid var(--secondary-color);
            background-color: #e0f2f1;
        }
        
        .url-display {
            font-family: monospace;
            background-color: #f5f5f5;
            padding: 0.5rem;
            border-radius: 2px;
            overflow-x: auto;
            font-size: 0.9rem;
        }
        
        .keyword-tag {
            display: inline-block;
            background-color: var(--primary-color);
            color: white;
            padding: 0.25rem 0.5rem;
            border-radius: 16px;
            font-size: 0.8rem;
            margin-right: 0.5rem;
        }
        
        .location-tag {
            display: inline-block;
            background-color: var(--secondary-color);
            color: white;
            padding: 0.25rem 0.5rem;
            border-radius: 16px;
            font-size: 0.8rem;
        }
        
        .content-preview {
            background-color: #f9f9f9;
            border: 1px solid #e0e0e0;
            padding: 0.75rem;
            border-radius: 4px;
            font-family: monospace;
            font-size: 0.9rem;
            margin-top: 0.5rem;
            white-space: pre-wrap;
            overflow-x: auto;
        }
        
        .action-button {
            margin-top: 1rem;
        }
        
        .progress-container {
            margin: 1rem 0;
        }
        
        .stProgress > div > div > div {
            background-color: var(--primary-color);
        }
        </style>
    """, unsafe_allow_html=True)

    # UI Components with improved styling
    st.markdown('<h1 class="main-header">Enhanced Web Crawler</h1>', unsafe_allow_html=True)
    st.write("Search for GoWithGuide and affiliate references on websites with improved detection capabilities.")
    
    # Create a card-like container for inputs
    st.markdown('<div class="results-box">', unsafe_allow_html=True)
    
    col1, col2 = st.columns([3, 1])
    with col1:
        url_input = st.text_input("Enter website URL:", "https://example.com", 
                                 help="Enter the full URL, including http:// or https://")
    with col2:
        crawl_mode = st.selectbox("Crawl Mode:", ["Quick", "Standard", "Complete"], index=1,
                                 help="Quick: Limited crawl, Standard: Moderate depth, Complete: Thorough crawl")
    
    col1, col2 = st.columns(2)
    with col1:
        start_btn = st.button("🔍 Start Crawling", help="Begin crawling the website")
    with col2:
        stop_btn = st.button("⛔ Stop & Reset", help="Stop the current crawl and reset")
    
    st.markdown('</div>', unsafe_allow_html=True)

    # Initialize session state
    if 'crawler' not in st.session_state:
        st.session_state.crawler = None
        st.session_state.running = False
        st.session_state.results = []
        st.session_state.status = []
        st.session_state.categories = []

    # Status and Results Display
    status_container = st.empty()
    progress_container = st.empty()
    results_container = st.empty()

    # Handle Start Button
    if start_btn and not st.session_state.running:
        if not url_input.startswith(('http://', 'https://')):
            url_input = f'https://{url_input}'
        st.session_state.crawler = EnhancedWebCrawler(start_url=url_input, crawl_mode=crawl_mode)
        st.session_state.running = True
        st.session_state.results = []
        st.session_state.status = [f"Starting crawl of {url_input} in {crawl_mode} mode"]
        st.session_state.categories = []

    # Handle Stop Button
    if stop_btn:
        st.session_state.running = False
        if st.session_state.crawler:
            st.session_state.status.append("Crawl stopped by user")
        st.session_state.crawler = None
        st.session_state.results = []
        st.session_state.status = []
        st.session_state.categories = []

    # Crawling Logic
    if st.session_state.running and st.session_state.crawler:
        crawler = st.session_state.crawler
        with progress_container.container():
            st.markdown('<div class="progress-container">', unsafe_allow_html=True)
            progress_bar = st.progress(0)
            st.markdown('</div>', unsafe_allow_html=True)
            
        total_pages = crawler.max_pages

        if crawler.crawl_mode == "Quick":
            urls_to_crawl = [crawler.start_url]
            for i, url in enumerate(urls_to_crawl):
                if not st.session_state.running:
                    break
                st.session_state.status.append(f"Crawling: {url}")
                crawler.process_url(url)
                st.session_state.results = crawler.results
                progress_bar.progress((i + 1) / len(urls_to_crawl))
            st.session_state.running = False

        elif crawler.crawl_mode == "Standard":
            if not st.session_state.categories:
                homepage_links = crawler.get_main_pages()
                st.session_state.status.append(f"Crawling homepage and {len(homepage_links)} main pages...")
                urls_to_crawl = [crawler.start_url] + homepage_links
                for i, url in enumerate(urls_to_crawl[:crawler.max_pages]):
                    if not st.session_state.running:
                        break
                    st.session_state.status.append(f"Crawling: {url}")
                    crawler.process_url(url)
                    st.session_state.results = crawler.results
                    progress_bar.progress((i + 1) / min(crawler.max_pages, len(urls_to_crawl)))
                    if crawler.results:
                        st.session_state.status.append(f"Found {len(crawler.results)} matches")
                        break
                if not crawler.results:
                    st.session_state.categories = crawler.extract_categories()
                    if st.session_state.categories:
                        st.session_state.status.append(f"Found categories: {', '.join([c[0] for c in st.session_state.categories])}")
                    else:
                        st.session_state.status.append("No categories found.")
                        st.session_state.running = False
            elif st.session_state.categories:
                cat_name, cat_url = st.session_state.categories.pop(0)
                st.session_state.status.append(f"Processing category: {cat_name}")
                category_links = crawler.get_category_pages(cat_url)
                for i, url in enumerate(category_links[:crawler.max_pages]):
                    if not st.session_state.running:
                        break
                    st.session_state.status.append(f"Crawling: {url}")
                    crawler.process_url(url)
                    st.session_state.results = crawler.results
                    progress_bar.progress((i + 1) / min(crawler.max_pages, len(category_links)))
                    if crawler.results:
                        st.session_state.status.append(f"Found {len(crawler.results)} matches")
                        break
                if not st.session_state.categories and not crawler.results:
                    st.session_state.running = False

        elif crawler.crawl_mode == "Complete":
            while crawler.queue and crawler.pages_crawled < crawler.max_pages and st.session_state.running:
                url = crawler.queue.popleft()
                if url not in crawler.visited:
                    st.session_state.status.append(f"Crawling: {url} (Page {crawler.pages_crawled + 1}/{crawler.max_pages})")
                    new_urls = crawler.process_url(url)
                    for new_url in new_urls:
                        if (new_url not in crawler.visited and 
                            new_url not in crawler.queue and 
                            crawler.pages_crawled < crawler.max_pages):
                            crawler.queue.append(new_url)
                    st.session_state.results = crawler.results
                    progress_bar.progress(min(crawler.pages_crawled / crawler.max_pages, 1.0))
                    if crawler.results:
                        st.session_state.status.append(f"Found {len(crawler.results)} matches")
            if crawler.pages_crawled >= crawler.max_pages or not crawler.queue:
                st.session_state.running = False

        # Display Status
        with status_container.container():
            st.markdown('<div class="status-box">', unsafe_allow_html=True)
            st.markdown('<h2 class="subheader">Status</h2>', unsafe_allow_html=True)
            for msg in st.session_state.status[-10:]:
                st.write(msg)
            st.markdown('</div>', unsafe_allow_html=True)

        # Display Results and Options
        if st.session_state.results:
            with results_container.container():
                st.markdown('<div class="results-box">', unsafe_allow_html=True)
                st.markdown(f'<h2 class="subheader">Matches Found ({len(st.session_state.results)})</h2>', unsafe_allow_html=True)
                
                for i, result in enumerate(st.session_state.results[-5:], 1):
                    st.markdown(f'<div class="match-item">', unsafe_allow_html=True)
                    st.markdown(f"**Match {i}:**", unsafe_allow_html=True)
                    
                    st.markdown(f"<div><strong>Source URL:</strong> <span class='url-display'>{html.escape(result['source_url'])}</span></div>", unsafe_allow_html=True)
                    st.markdown(f"<div><strong>Matched URL:</strong> <span class='url-display'>{html.escape(result['matched_url'])}</span></div>", unsafe_allow_html=True)
                    
                    st.markdown(f"<div><span class='keyword-tag'>{html.escape(result['keyword'])}</span> <span class='location-tag'>{html.escape(result['location_type'])}</span></div>", unsafe_allow_html=True)
                    
                    st.markdown(f"<div><strong>Element:</strong> {html.escape(result['element'])} [{html.escape(result['attribute'])}]</div>", unsafe_allow_html=True)
                    
                    if result['content']:
                        content_preview = result['content'][:100] + ('...' if len(result['content']) > 100 else '')
                        st.markdown(f"<div><strong>Content:</strong> <div class='content-preview'>{html.escape(content_preview)}</div></div>", unsafe_allow_html=True)
                        
                    st.markdown('</div>', unsafe_allow_html=True)
                
                col1, col2, col3 = st.columns(3)
                with col1:
                    if st.button("💾 Save Results & Stop", key="save_results"):
                        csv_data = generate_csv(crawler.results)
                        st.download_button(
                            label="📥 Download CSV",
                            data=csv_data,
                            file_name=f"crawl_report_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.csv",
                            mime="text/csv"
                        )
                        st.session_state.running = False
                        crawler.user_stopped = True
                with col2:
                    if st.button("🔄 Continue to Next Category", key="next_category") and crawler.crawl_mode != "Complete":
                        crawler.pages_crawled = 0
                with col3:
                    if st.button("⏩ Continue Current Category", key="current_category") and crawler.crawl_mode != "Complete":
                        crawler.pages_crawled = 0
                st.markdown('</div>', unsafe_allow_html=True)

        # Final Report
        if not st.session_state.running and st.session_state.results and not crawler.user_stopped:
            csv_data = generate_csv(crawler.results)
            st.download_button(
                label="📥 Download Final Results",
                data=csv_data,
                file_name=f"crawl_report_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.csv",
                mime="text/csv"
            )

if __name__ == "__main__":
    main()
